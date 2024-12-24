require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1482716 (x : El real) (a : El real) (b : El real) (y : El real) (c : El real) (r : El real) : Prf (∧ (= (real_gt (real_add a (real_min x y)) r) (∧ (real_gt (real_add a x) r) (real_gt (real_add a y) r))) (∧ (= (real_gt (real_add a (real_add (real_min x y) b)) r) (∧ (real_gt (real_add a (real_add x b)) r) (real_gt (real_add a (real_add y b)) r))) (∧ (= (real_gt (real_add a (real_add b (real_min x y))) r) (∧ (real_gt (real_add a (real_add b x)) r) (real_gt (real_add a (real_add b y)) r))) (= (real_gt (real_add a (real_add b (real_add (real_min x y) c))) r) (∧ (real_gt (real_add a (real_add b (real_add x c))) r) (real_gt (real_add a (real_add b (real_add y c))) r))))));
