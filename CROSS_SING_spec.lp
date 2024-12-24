require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4327265 [A B] : Prf (∀ (λ x : El A, (∀ (λ y : El B, (= ((@CROSS B A) ((@INSERT A) x (@EMPTY A)) ((@INSERT B) y (@EMPTY B))) ((@INSERT (prod A B)) ((@̦‚ A B) x y) (@EMPTY (prod A B))))))));
