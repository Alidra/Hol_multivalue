require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1352530 (n : El real) (m : El real) (p : El real) : Prf (∧ (= (real_add m n) (real_add n m)) (∧ (= (real_add (real_add m n) p) (real_add m (real_add n p))) (= (real_add m (real_add n p)) (real_add n (real_add m p)))));
