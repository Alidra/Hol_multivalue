require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1009124 (p : El num) (b : El num) (m : El num) (n : El num) (a : El num) : Prf (⇒ (= (EXP m n) p) (⇒ (= (* p p) b) (⇒ (= (* m b) a) (= (EXP m (BIT1 n)) a))));
