require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1325510 : Prf (∀ (λ y : El hreal, (∀ (λ x : El hreal, (= (treal_inv ((@̦‚ hreal hreal) x y)) ((@COND (prod hreal hreal)) (= x y) ((@̦‚ hreal hreal) (hreal_of_num (NUMERAL _0)) (hreal_of_num (NUMERAL _0))) ((@COND (prod hreal hreal)) (hreal_le y x) ((@̦‚ hreal hreal) (hreal_inv ((@ε hreal) (λ d : El hreal, (= x (hreal_add y d))))) (hreal_of_num (NUMERAL _0))) ((@̦‚ hreal hreal) (hreal_of_num (NUMERAL _0)) (hreal_inv ((@ε hreal) (λ d : El hreal, (= y (hreal_add x d)))))))))))));
