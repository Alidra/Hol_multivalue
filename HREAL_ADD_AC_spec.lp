require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1322003 (n : El hreal) (m : El hreal) (p : El hreal) : Prf (∧ (= (hreal_add m n) (hreal_add n m)) (∧ (= (hreal_add (hreal_add m n) p) (hreal_add m (hreal_add n p))) (= (hreal_add m (hreal_add n p)) (hreal_add n (hreal_add m p)))));
