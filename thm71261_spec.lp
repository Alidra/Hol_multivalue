require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem71261 (r : El ind) : Prf (= (NUM_REP r) (= (dest_num (mk_num r)) r));
