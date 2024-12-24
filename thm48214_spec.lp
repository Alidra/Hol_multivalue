require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48214 [A B] (x : El A) (y : El B) : Prf (= ((λ y' : El B, (= ((@SND A B) ((@̦‚ A B) x y')) y')) y) (= ((@SND A B) ((@̦‚ A B) x y)) y));
