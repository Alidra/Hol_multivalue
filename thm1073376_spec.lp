require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1073376 [A B] (x : El A) (a : El A) (y : El B) (b : El B) : Prf (= ((λ b' : El B, (= (= ((@̦‚ A B) x y) ((@̦‚ A B) a b')) (∧ (= x a) (= y b')))) b) (= (= ((@̦‚ A B) x y) ((@̦‚ A B) a b)) (∧ (= x a) (= y b))));
