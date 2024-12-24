require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301028 (n : El int) (m : El int) (p : El int) : Prf (∧ (= (int_add m n) (int_add n m)) (∧ (= (int_add (int_add m n) p) (int_add m (int_add n p))) (= (int_add m (int_add n p)) (int_add n (int_add m p)))));
