require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1009021 (p : El num) (m : El num) (n : El num) (a : El num) : Prf (⇒ (= (EXP m n) p) (⇒ (= (* p p) a) (= (EXP m (BIT0 n)) a)));
