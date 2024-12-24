require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem618 (q : El bool) (p : El bool) (r : El bool) : Prf (= (∧ p (∧ q r)) (∧ q (∧ p r)));
