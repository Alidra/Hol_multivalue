require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301003 (m : El int) (n : El int) (p : El int) : Prf (= (int_add (int_add m n) p) (int_add m (int_add n p)));
