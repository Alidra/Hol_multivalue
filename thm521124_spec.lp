require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem521124 (n : El num) (m : El num) : Prf (⇒ (¬ (∧ (<= m n) (< n m))) (= (∧ (<= m n) (< n m)) F));
