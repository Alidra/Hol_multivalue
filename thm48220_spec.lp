require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48220 [A B] (y : El B) (x : El A) : Prf (= ((λ y' : El B, (= ((@FST A B) ((@̦‚ A B) x y')) x)) y) (= ((@FST A B) ((@̦‚ A B) x y)) x));
